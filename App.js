import { StatusBar } from 'expo-status-bar';
import React, { useState, useEffect, useRef } from 'react';
import {
  StyleSheet,
  Text,
  View,
  ScrollView,
  TouchableOpacity,
  Switch,
  Alert,
  Platform,
  Animated,
  TextInput,
  FlatList,
  Image,
  Dimensions,
} from 'react-native';
import { LinearGradient } from 'expo-linear-gradient';
import { BlurView } from 'expo-blur';
import * as Haptics from 'expo-haptics';
import * as Clipboard from 'expo-clipboard';
import * as Linking from 'expo-linking';
import * as WebBrowser from 'expo-web-browser';
import Constants from 'expo-constants';
import * as Device from 'expo-device';
import * as Network from 'expo-network';
import { Ionicons, MaterialIcons, FontAwesome5, AntDesign } from '@expo/vector-icons';
import { SafeAreaProvider, SafeAreaView } from 'react-native-safe-area-context';

const { width: SCREEN_WIDTH } = Dimensions.get('window');

const TABS = ['Home', 'Widgets', 'Sensors', 'Device', 'About'];

// ─── SECTION CARD ────────────────────────────────────────────────────────────
function Card({ title, icon, children, color = '#6C63FF' }) {
  return (
    <View style={styles.card}>
      <View style={[styles.cardHeader, { backgroundColor: color }]}>
        <Text style={styles.cardIcon}>{icon}</Text>
        <Text style={styles.cardTitle}>{title}</Text>
      </View>
      <View style={styles.cardBody}>{children}</View>
    </View>
  );
}

// ─── HOME TAB ────────────────────────────────────────────────────────────────
function HomeTab() {
  const fadeAnim = useRef(new Animated.Value(0)).current;
  const slideAnim = useRef(new Animated.Value(40)).current;

  useEffect(() => {
    Animated.parallel([
      Animated.timing(fadeAnim, { toValue: 1, duration: 800, useNativeDriver: true }),
      Animated.timing(slideAnim, { toValue: 0, duration: 800, useNativeDriver: true }),
    ]).start();
  }, []);

  const features = [
    { icon: '📷', label: 'Camera' },
    { icon: '📍', label: 'Location' },
    { icon: '🔔', label: 'Notifications' },
    { icon: '📳', label: 'Haptics' },
    { icon: '🌐', label: 'Web Browser' },
    { icon: '📋', label: 'Clipboard' },
    { icon: '🔋', label: 'Battery' },
    { icon: '📶', label: 'Network' },
    { icon: '📱', label: 'Device' },
    { icon: '🎵', label: 'Audio/Video' },
    { icon: '🧭', label: 'Sensors' },
    { icon: '🔗', label: 'Deep Links' },
  ];

  return (
    <ScrollView contentContainerStyle={styles.tabContent}>
      <LinearGradient colors={['#6C63FF', '#3B82F6', '#06B6D4']} style={styles.hero}>
        <Animated.View style={{ opacity: fadeAnim, transform: [{ translateY: slideAnim }] }}>
          <Text style={styles.heroTitle}>Expo Showcase</Text>
          <Text style={styles.heroSubtitle}>All the best Expo widgets in one app</Text>
          <View style={styles.heroBadge}>
            <Text style={styles.heroBadgeText}>⚡ Powered by Expo SDK 54</Text>
          </View>
        </Animated.View>
      </LinearGradient>

      <View style={styles.featureGrid}>
        {features.map((f) => (
          <View key={f.label} style={styles.featureItem}>
            <Text style={styles.featureIcon}>{f.icon}</Text>
            <Text style={styles.featureLabel}>{f.label}</Text>
          </View>
        ))}
      </View>

      <Card title="Quick Actions" icon="⚡" color="#F59E0B">
        <TouchableOpacity
          style={[styles.btn, { backgroundColor: '#6C63FF' }]}
          onPress={() => WebBrowser.openBrowserAsync('https://expo.dev')}
        >
          <Ionicons name="globe-outline" size={16} color="#fff" />
          <Text style={styles.btnText}>Open Expo Docs</Text>
        </TouchableOpacity>
        <TouchableOpacity
          style={[styles.btn, { backgroundColor: '#10B981', marginTop: 8 }]}
          onPress={async () => {
            await Clipboard.setStringAsync('Hello from Expo Showcase! 🚀');
            Alert.alert('Copied!', 'Text copied to clipboard');
          }}
        >
          <Ionicons name="copy-outline" size={16} color="#fff" />
          <Text style={styles.btnText}>Copy to Clipboard</Text>
        </TouchableOpacity>
        <TouchableOpacity
          style={[styles.btn, { backgroundColor: '#EF4444', marginTop: 8 }]}
          onPress={() => {
            if (Platform.OS !== 'web') Haptics.impactAsync(Haptics.ImpactFeedbackStyle.Heavy);
            Alert.alert('Haptics!', 'Haptic feedback triggered (on native)');
          }}
        >
          <Ionicons name="phone-portrait-outline" size={16} color="#fff" />
          <Text style={styles.btnText}>Trigger Haptics</Text>
        </TouchableOpacity>
      </Card>
    </ScrollView>
  );
}

// ─── WIDGETS TAB ─────────────────────────────────────────────────────────────
function WidgetsTab() {
  const [switchVal, setSwitchVal] = useState(false);
  const [text, setText] = useState('');
  const [sliderVal, setSliderVal] = useState(0.5);
  const [count, setCount] = useState(0);
  const [activeChip, setActiveChip] = useState('All');
  const progressAnim = useRef(new Animated.Value(0)).current;

  const chips = ['All', 'React Native', 'Expo', 'UI'];

  useEffect(() => {
    Animated.timing(progressAnim, { toValue: 0.72, duration: 1200, useNativeDriver: false }).start();
  }, []);

  const barWidth = progressAnim.interpolate({ inputRange: [0, 1], outputRange: ['0%', '100%'] });

  const listItems = [
    { id: '1', icon: '🎨', title: 'LinearGradient', desc: 'Smooth color transitions' },
    { id: '2', icon: '🌫️', title: 'BlurView', desc: 'Frosted-glass effects' },
    { id: '3', icon: '📳', title: 'Haptics', desc: 'Tactile feedback' },
    { id: '4', icon: '📋', title: 'Clipboard', desc: 'Copy & paste text' },
    { id: '5', icon: '🔗', title: 'Linking', desc: 'Open URLs & deep links' },
    { id: '6', icon: '🌐', title: 'WebBrowser', desc: 'In-app browser' },
    { id: '7', icon: '🔤', title: 'Google Fonts', desc: 'expo-font integration' },
    { id: '8', icon: '💾', title: 'SecureStore', desc: 'Encrypted key-value store' },
    { id: '9', icon: '📁', title: 'FileSystem', desc: 'File read/write access' },
    { id: '10', icon: '🔐', title: 'Constants', desc: 'App & Expo constants' },
  ];

  return (
    <ScrollView contentContainerStyle={styles.tabContent}>
      <Card title="Gradient & Blur" icon="🎨" color="#8B5CF6">
        <LinearGradient
          colors={['#FF6B6B', '#FFE66D', '#4ECDC4']}
          start={{ x: 0, y: 0 }}
          end={{ x: 1, y: 0 }}
          style={styles.gradientBox}
        >
          <Text style={styles.gradientText}>LinearGradient</Text>
        </LinearGradient>
        {Platform.OS !== 'web' ? (
          <BlurView intensity={50} style={styles.blurBox}>
            <Text style={styles.blurText}>BlurView (native only)</Text>
          </BlurView>
        ) : (
          <View style={[styles.blurBox, { backgroundColor: 'rgba(108,99,255,0.15)' }]}>
            <Text style={styles.blurText}>BlurView (simulated on web)</Text>
          </View>
        )}
      </Card>

      <Card title="Controls" icon="🎛️" color="#EC4899">
        <View style={styles.row}>
          <Text style={styles.label}>Toggle Switch</Text>
          <Switch
            value={switchVal}
            onValueChange={setSwitchVal}
            trackColor={{ false: '#ccc', true: '#6C63FF' }}
            thumbColor={switchVal ? '#fff' : '#fff'}
          />
        </View>
        <TextInput
          style={styles.input}
          placeholder="Type something..."
          value={text}
          onChangeText={setText}
          placeholderTextColor="#aaa"
        />
        {text ? <Text style={styles.inputPreview}>You typed: {text}</Text> : null}
        <View style={styles.counterRow}>
          <TouchableOpacity style={styles.counterBtn} onPress={() => setCount((c) => c - 1)}>
            <AntDesign name="minuscircleo" size={28} color="#EF4444" />
          </TouchableOpacity>
          <Text style={styles.counterVal}>{count}</Text>
          <TouchableOpacity style={styles.counterBtn} onPress={() => setCount((c) => c + 1)}>
            <AntDesign name="pluscircleo" size={28} color="#10B981" />
          </TouchableOpacity>
        </View>
      </Card>

      <Card title="Animated Progress" icon="📊" color="#F59E0B">
        <Text style={styles.progressLabel}>Loading… 72%</Text>
        <View style={styles.progressTrack}>
          <Animated.View style={[styles.progressFill, { width: barWidth }]} />
        </View>
        <View style={styles.chipRow}>
          {chips.map((c) => (
            <TouchableOpacity
              key={c}
              style={[styles.chip, activeChip === c && styles.chipActive]}
              onPress={() => setActiveChip(c)}
            >
              <Text style={[styles.chipText, activeChip === c && styles.chipTextActive]}>{c}</Text>
            </TouchableOpacity>
          ))}
        </View>
      </Card>

      <Card title="Expo Package List" icon="📦" color="#06B6D4">
        {listItems.map((item) => (
          <View key={item.id} style={styles.listRow}>
            <Text style={styles.listIcon}>{item.icon}</Text>
            <View style={{ flex: 1 }}>
              <Text style={styles.listTitle}>{item.title}</Text>
              <Text style={styles.listDesc}>{item.desc}</Text>
            </View>
            <Ionicons name="checkmark-circle" size={20} color="#10B981" />
          </View>
        ))}
      </Card>

      <Card title="Vector Icons Showcase" icon="🎯" color="#3B82F6">
        <View style={styles.iconGrid}>
          {[
            { lib: 'Ionicons', name: 'home', color: '#6C63FF' },
            { lib: 'Ionicons', name: 'heart', color: '#EF4444' },
            { lib: 'Ionicons', name: 'star', color: '#F59E0B' },
            { lib: 'Ionicons', name: 'camera', color: '#10B981' },
            { lib: 'Ionicons', name: 'musical-notes', color: '#8B5CF6' },
            { lib: 'Ionicons', name: 'rocket', color: '#06B6D4' },
            { lib: 'Ionicons', name: 'flash', color: '#F97316' },
            { lib: 'Ionicons', name: 'globe', color: '#3B82F6' },
            { lib: 'Ionicons', name: 'settings', color: '#6B7280' },
            { lib: 'Ionicons', name: 'mail', color: '#EC4899' },
            { lib: 'Ionicons', name: 'map', color: '#84CC16' },
            { lib: 'Ionicons', name: 'game-controller', color: '#A78BFA' },
          ].map((icon) => (
            <View key={icon.name} style={styles.iconItem}>
              <Ionicons name={icon.name} size={32} color={icon.color} />
              <Text style={styles.iconLabel}>{icon.name}</Text>
            </View>
          ))}
        </View>
      </Card>
    </ScrollView>
  );
}

// ─── SENSORS TAB ─────────────────────────────────────────────────────────────
function SensorsTab() {
  const [accel, setAccel] = useState({ x: 0, y: 0, z: 0 });
  const [gyro, setGyro] = useState({ x: 0, y: 0, z: 0 });
  const [network, setNetwork] = useState(null);

  useEffect(() => {
    let accelSub, gyroSub;
    (async () => {
      try {
        const { Accelerometer, Gyroscope } = await import('expo-sensors');
        Accelerometer.setUpdateInterval(500);
        accelSub = Accelerometer.addListener(setAccel);
        Gyroscope.setUpdateInterval(500);
        gyroSub = Gyroscope.addListener(setGyro);
      } catch (e) {}

      try {
        const netState = await Network.getNetworkStateAsync();
        setNetwork(netState);
      } catch (e) {}
    })();
    return () => {
      accelSub?.remove();
      gyroSub?.remove();
    };
  }, []);

  const fmtVal = (v) => (v?.toFixed(3) ?? '—');

  return (
    <ScrollView contentContainerStyle={styles.tabContent}>
      <Card title="Accelerometer" icon="🧭" color="#6C63FF">
        {[
          { axis: 'X', val: accel.x, color: '#EF4444' },
          { axis: 'Y', val: accel.y, color: '#10B981' },
          { axis: 'Z', val: accel.z, color: '#3B82F6' },
        ].map(({ axis, val, color }) => (
          <View key={axis} style={styles.sensorRow}>
            <Text style={[styles.sensorAxis, { color }]}>{axis}</Text>
            <View style={styles.sensorBarTrack}>
              <View
                style={[
                  styles.sensorBarFill,
                  { backgroundColor: color, width: `${Math.min(100, Math.abs(val) * 50)}%` },
                ]}
              />
            </View>
            <Text style={styles.sensorVal}>{fmtVal(val)}</Text>
          </View>
        ))}
        <Text style={styles.sensorNote}>Live data — tilt your device!</Text>
      </Card>

      <Card title="Gyroscope" icon="🌀" color="#8B5CF6">
        {[
          { axis: 'X', val: gyro.x, color: '#EF4444' },
          { axis: 'Y', val: gyro.y, color: '#10B981' },
          { axis: 'Z', val: gyro.z, color: '#3B82F6' },
        ].map(({ axis, val, color }) => (
          <View key={axis} style={styles.sensorRow}>
            <Text style={[styles.sensorAxis, { color }]}>{axis}</Text>
            <View style={styles.sensorBarTrack}>
              <View
                style={[
                  styles.sensorBarFill,
                  { backgroundColor: color, width: `${Math.min(100, Math.abs(val) * 20)}%` },
                ]}
              />
            </View>
            <Text style={styles.sensorVal}>{fmtVal(val)}</Text>
          </View>
        ))}
        <Text style={styles.sensorNote}>Rotate your device to see values change</Text>
      </Card>

      <Card title="Network" icon="📶" color="#06B6D4">
        <View style={styles.infoRow}>
          <FontAwesome5 name="wifi" size={16} color="#06B6D4" />
          <Text style={styles.infoLabel}>Connected</Text>
          <Text style={styles.infoVal}>{network?.isConnected ? '✅ Yes' : '❌ No'}</Text>
        </View>
        <View style={styles.infoRow}>
          <FontAwesome5 name="network-wired" size={16} color="#06B6D4" />
          <Text style={styles.infoLabel}>Type</Text>
          <Text style={styles.infoVal}>{network?.type ?? '—'}</Text>
        </View>
        <View style={styles.infoRow}>
          <FontAwesome5 name="check-circle" size={16} color="#06B6D4" />
          <Text style={styles.infoLabel}>Internet Reachable</Text>
          <Text style={styles.infoVal}>{network?.isInternetReachable ? '✅ Yes' : '❌ No'}</Text>
        </View>
      </Card>
    </ScrollView>
  );
}

// ─── DEVICE TAB ──────────────────────────────────────────────────────────────
function DeviceTab() {
  const [clipText, setClipText] = useState('');

  const deviceInfo = [
    { label: 'Brand', val: Device.brand ?? '—' },
    { label: 'Model', val: Device.modelName ?? '—' },
    { label: 'OS Name', val: Device.osName ?? '—' },
    { label: 'OS Version', val: Device.osVersion ?? '—' },
    { label: 'Device Type', val: String(Device.deviceType ?? '—') },
    { label: 'Is Device', val: Device.isDevice ? '✅ Physical' : '🖥️ Simulator' },
    { label: 'Total Memory', val: Device.totalMemory ? `${(Device.totalMemory / 1e9).toFixed(1)} GB` : '—' },
  ];

  const constantsInfo = [
    { label: 'App Name', val: Constants.expoConfig?.name ?? '—' },
    { label: 'SDK Version', val: Constants.expoConfig?.sdkVersion ?? '—' },
    { label: 'Platform', val: Platform.OS },
    { label: 'Expo Version', val: Constants.expoVersion ?? '—' },
  ];

  return (
    <ScrollView contentContainerStyle={styles.tabContent}>
      <Card title="Device Info" icon="📱" color="#F59E0B">
        {deviceInfo.map(({ label, val }) => (
          <View key={label} style={styles.infoRow}>
            <Text style={styles.infoLabel}>{label}</Text>
            <Text style={styles.infoVal}>{val}</Text>
          </View>
        ))}
      </Card>

      <Card title="App Constants" icon="🔐" color="#10B981">
        {constantsInfo.map(({ label, val }) => (
          <View key={label} style={styles.infoRow}>
            <Text style={styles.infoLabel}>{label}</Text>
            <Text style={styles.infoVal}>{val}</Text>
          </View>
        ))}
      </Card>

      <Card title="Clipboard" icon="📋" color="#EC4899">
        <TouchableOpacity
          style={[styles.btn, { backgroundColor: '#EC4899' }]}
          onPress={async () => {
            const t = await Clipboard.getStringAsync();
            setClipText(t || '(empty)');
          }}
        >
          <Ionicons name="clipboard-outline" size={16} color="#fff" />
          <Text style={styles.btnText}>Paste from Clipboard</Text>
        </TouchableOpacity>
        {clipText ? (
          <View style={styles.clipPreview}>
            <Text style={styles.clipPreviewText}>{clipText}</Text>
          </View>
        ) : null}
      </Card>

      <Card title="Deep Linking" icon="🔗" color="#3B82F6">
        <TouchableOpacity
          style={[styles.btn, { backgroundColor: '#3B82F6' }]}
          onPress={() => Linking.openURL('https://github.com/domthedeveloper/test-expo-app')}
        >
          <Ionicons name="logo-github" size={16} color="#fff" />
          <Text style={styles.btnText}>Open GitHub Repo</Text>
        </TouchableOpacity>
        <TouchableOpacity
          style={[styles.btn, { backgroundColor: '#6C63FF', marginTop: 8 }]}
          onPress={() => WebBrowser.openBrowserAsync('https://docs.expo.dev')}
        >
          <Ionicons name="book-outline" size={16} color="#fff" />
          <Text style={styles.btnText}>Open Expo Docs (in-app)</Text>
        </TouchableOpacity>
      </Card>
    </ScrollView>
  );
}

// ─── ABOUT TAB ───────────────────────────────────────────────────────────────
function AboutTab() {
  const packages = [
    'expo-camera', 'expo-image-picker', 'expo-location', 'expo-sensors',
    'expo-av', 'expo-haptics', 'expo-linear-gradient', 'expo-blur',
    'expo-font', 'expo-web-browser', 'expo-linking', 'expo-constants',
    'expo-device', 'expo-battery', 'expo-brightness', 'expo-clipboard',
    'expo-file-system', 'expo-network', 'expo-secure-store', '@expo/vector-icons',
    'react-native-reanimated', 'react-native-gesture-handler',
  ];

  return (
    <ScrollView contentContainerStyle={styles.tabContent}>
      <LinearGradient colors={['#1e1b4b', '#312e81', '#4338ca']} style={styles.aboutHero}>
        <Text style={styles.aboutTitle}>Expo Showcase</Text>
        <Text style={styles.aboutVersion}>v1.0.0 · SDK 54</Text>
        <Text style={styles.aboutTagline}>A comprehensive demo of Expo widgets & APIs</Text>
      </LinearGradient>

      <Card title="Included Packages" icon="📦" color="#4338CA">
        <View style={styles.packageGrid}>
          {packages.map((pkg) => (
            <View key={pkg} style={styles.packageBadge}>
              <Text style={styles.packageText}>{pkg}</Text>
            </View>
          ))}
        </View>
      </Card>

      <Card title="Built With" icon="🛠️" color="#7C3AED">
        {[
          { icon: '⚛️', name: 'React Native 0.81' },
          { icon: '📱', name: 'Expo SDK 54' },
          { icon: '🌐', name: 'Expo Web (Metro bundler)' },
          { icon: '🚀', name: 'GitHub Pages deployment' },
          { icon: '🤖', name: 'GitHub Actions CI/CD' },
        ].map(({ icon, name }) => (
          <View key={name} style={styles.listRow}>
            <Text style={styles.listIcon}>{icon}</Text>
            <Text style={styles.listTitle}>{name}</Text>
          </View>
        ))}
      </Card>
    </ScrollView>
  );
}

// ─── ROOT APP ────────────────────────────────────────────────────────────────
export default function App() {
  const [activeTab, setActiveTab] = useState('Home');

  const renderTab = () => {
    switch (activeTab) {
      case 'Home': return <HomeTab />;
      case 'Widgets': return <WidgetsTab />;
      case 'Sensors': return <SensorsTab />;
      case 'Device': return <DeviceTab />;
      case 'About': return <AboutTab />;
      default: return <HomeTab />;
    }
  };

  return (
    <SafeAreaProvider>
      <SafeAreaView style={styles.root}>
        <StatusBar style="light" />
        <LinearGradient colors={['#1e1b4b', '#312e81']} style={styles.topBar}>
          <Text style={styles.topBarTitle}>⚡ Expo Showcase</Text>
        </LinearGradient>
        <View style={styles.tabBar}>
          {TABS.map((tab) => (
            <TouchableOpacity
              key={tab}
              style={[styles.tabItem, activeTab === tab && styles.tabItemActive]}
              onPress={() => setActiveTab(tab)}
            >
              <Text style={[styles.tabText, activeTab === tab && styles.tabTextActive]}>{tab}</Text>
            </TouchableOpacity>
          ))}
        </View>
        <View style={{ flex: 1 }}>{renderTab()}</View>
      </SafeAreaView>
    </SafeAreaProvider>
  );
}

// ─── STYLES ──────────────────────────────────────────────────────────────────
const styles = StyleSheet.create({
  root: { flex: 1, backgroundColor: '#F3F4F6' },
  topBar: { paddingVertical: 12, paddingHorizontal: 16 },
  topBarTitle: { color: '#fff', fontSize: 18, fontWeight: '700' },

  tabBar: { flexDirection: 'row', backgroundColor: '#fff', borderBottomWidth: 1, borderBottomColor: '#E5E7EB' },
  tabItem: { flex: 1, paddingVertical: 10, alignItems: 'center' },
  tabItemActive: { borderBottomWidth: 2, borderBottomColor: '#6C63FF' },
  tabText: { fontSize: 11, color: '#9CA3AF', fontWeight: '500' },
  tabTextActive: { color: '#6C63FF', fontWeight: '700' },

  tabContent: { padding: 16, paddingBottom: 40 },

  // Hero
  hero: { borderRadius: 16, padding: 24, marginBottom: 16, alignItems: 'center' },
  heroTitle: { fontSize: 28, fontWeight: '800', color: '#fff', textAlign: 'center' },
  heroSubtitle: { fontSize: 14, color: 'rgba(255,255,255,0.85)', marginTop: 4, textAlign: 'center' },
  heroBadge: { marginTop: 12, backgroundColor: 'rgba(255,255,255,0.2)', borderRadius: 20, paddingHorizontal: 16, paddingVertical: 6 },
  heroBadgeText: { color: '#fff', fontWeight: '600', fontSize: 12 },

  // Feature grid
  featureGrid: { flexDirection: 'row', flexWrap: 'wrap', marginBottom: 16 },
  featureItem: { width: '25%', alignItems: 'center', paddingVertical: 12 },
  featureIcon: { fontSize: 24 },
  featureLabel: { fontSize: 10, color: '#6B7280', marginTop: 4, fontWeight: '500' },

  // Card
  card: { backgroundColor: '#fff', borderRadius: 16, marginBottom: 16, overflow: 'hidden', shadowColor: '#000', shadowOffset: { width: 0, height: 2 }, shadowOpacity: 0.08, shadowRadius: 8, elevation: 3 },
  cardHeader: { flexDirection: 'row', alignItems: 'center', padding: 14 },
  cardIcon: { fontSize: 18, marginRight: 8 },
  cardTitle: { color: '#fff', fontWeight: '700', fontSize: 15 },
  cardBody: { padding: 16 },

  // Buttons
  btn: { flexDirection: 'row', alignItems: 'center', justifyContent: 'center', borderRadius: 10, paddingVertical: 10, paddingHorizontal: 16, gap: 8 },
  btnText: { color: '#fff', fontWeight: '600', fontSize: 14 },

  // Controls
  row: { flexDirection: 'row', alignItems: 'center', justifyContent: 'space-between', marginBottom: 12 },
  label: { color: '#374151', fontWeight: '500' },
  input: { borderWidth: 1, borderColor: '#E5E7EB', borderRadius: 10, padding: 10, fontSize: 14, color: '#111', backgroundColor: '#F9FAFB' },
  inputPreview: { marginTop: 6, color: '#6C63FF', fontStyle: 'italic', fontSize: 13 },
  counterRow: { flexDirection: 'row', alignItems: 'center', justifyContent: 'center', marginTop: 12, gap: 24 },
  counterBtn: {},
  counterVal: { fontSize: 28, fontWeight: '800', color: '#1F2937', minWidth: 40, textAlign: 'center' },

  // Progress
  progressLabel: { color: '#374151', fontWeight: '600', marginBottom: 8 },
  progressTrack: { height: 10, backgroundColor: '#E5E7EB', borderRadius: 5, overflow: 'hidden', marginBottom: 16 },
  progressFill: { height: '100%', backgroundColor: '#6C63FF', borderRadius: 5 },
  chipRow: { flexDirection: 'row', flexWrap: 'wrap', gap: 8 },
  chip: { borderWidth: 1, borderColor: '#E5E7EB', borderRadius: 20, paddingHorizontal: 14, paddingVertical: 6 },
  chipActive: { backgroundColor: '#6C63FF', borderColor: '#6C63FF' },
  chipText: { color: '#6B7280', fontSize: 13, fontWeight: '500' },
  chipTextActive: { color: '#fff' },

  // Gradient / Blur
  gradientBox: { height: 60, borderRadius: 10, justifyContent: 'center', alignItems: 'center', marginBottom: 10 },
  gradientText: { color: '#fff', fontWeight: '700', fontSize: 16 },
  blurBox: { height: 60, borderRadius: 10, justifyContent: 'center', alignItems: 'center' },
  blurText: { color: '#374151', fontWeight: '600' },

  // List
  listRow: { flexDirection: 'row', alignItems: 'center', paddingVertical: 8, borderBottomWidth: 1, borderBottomColor: '#F3F4F6', gap: 10 },
  listIcon: { fontSize: 20 },
  listTitle: { fontWeight: '600', color: '#1F2937', fontSize: 14 },
  listDesc: { color: '#6B7280', fontSize: 12, marginTop: 1 },

  // Icon grid
  iconGrid: { flexDirection: 'row', flexWrap: 'wrap' },
  iconItem: { width: '25%', alignItems: 'center', paddingVertical: 12 },
  iconLabel: { fontSize: 10, color: '#6B7280', marginTop: 4 },

  // Sensors
  sensorRow: { flexDirection: 'row', alignItems: 'center', marginBottom: 8, gap: 8 },
  sensorAxis: { width: 16, fontWeight: '700', fontSize: 14 },
  sensorBarTrack: { flex: 1, height: 8, backgroundColor: '#E5E7EB', borderRadius: 4, overflow: 'hidden' },
  sensorBarFill: { height: '100%', borderRadius: 4 },
  sensorVal: { width: 60, textAlign: 'right', fontSize: 12, color: '#374151', fontFamily: Platform.OS === 'ios' ? 'Menlo' : 'monospace' },
  sensorNote: { marginTop: 8, color: '#9CA3AF', fontSize: 12, fontStyle: 'italic', textAlign: 'center' },

  // Info rows
  infoRow: { flexDirection: 'row', alignItems: 'center', paddingVertical: 7, borderBottomWidth: 1, borderBottomColor: '#F3F4F6', gap: 8 },
  infoLabel: { flex: 1, color: '#6B7280', fontSize: 13 },
  infoVal: { color: '#1F2937', fontWeight: '600', fontSize: 13 },

  // Clipboard
  clipPreview: { marginTop: 12, backgroundColor: '#F3F4F6', borderRadius: 8, padding: 10 },
  clipPreviewText: { color: '#374151', fontSize: 13 },

  // About
  aboutHero: { borderRadius: 16, padding: 28, marginBottom: 16, alignItems: 'center' },
  aboutTitle: { fontSize: 28, fontWeight: '800', color: '#fff' },
  aboutVersion: { color: 'rgba(255,255,255,0.7)', marginTop: 4, fontSize: 13 },
  aboutTagline: { color: 'rgba(255,255,255,0.85)', marginTop: 8, fontSize: 14, textAlign: 'center' },

  // Packages
  packageGrid: { flexDirection: 'row', flexWrap: 'wrap', gap: 8 },
  packageBadge: { backgroundColor: '#EEF2FF', borderRadius: 6, paddingHorizontal: 10, paddingVertical: 5 },
  packageText: { color: '#4338CA', fontSize: 11, fontWeight: '600' },
});
